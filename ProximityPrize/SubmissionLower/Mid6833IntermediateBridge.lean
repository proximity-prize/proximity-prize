/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0. Intermediate-score extension of the 69.69 genuine-seed reduction.
The comparison and case split build on Lucieno, BitWonka and Bome2017. -/
import ProximityPrize.SubmissionLower.Mid6833GenuineResidual
namespace ProximityPrize.SubmissionLower.Intermediate
open ProximityPrize.Benchmark K6969Global Koala6831Separation Koala6831Comparison Koala6831Ordinary Genuine6969
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes coefficientDeterminant)
open Koala6831BenchmarkField (prime frobenius)
open Frontier6969.GenuineMoving Polynomial
open CoreDefinitions ProximityGap ToyProblem
open scoped Polynomial Classical NNReal
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
variable {K I : Type} [Field K] [Fintype I]
local instance mid6833Local_IntermediateBridge_15  : DecidableEq IRSProfile.Field := Classical.decEq _
local instance mid6833Local_IntermediateBridge_16  : DecidableEq IRSProfile.Index := Classical.decEq _
private theorem one_sided_price :
    max ((262144-131071:ℕ)*(7*(prime+1))/(179740-131071))
      ((131071+1)*(6*(prime+1))+(82404+1)) = 1675655722385893 := by decide +kernel
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

private theorem card_le_from_primitive_cases
    (x : I ↪ K) (u v : Fin 2 → I → K) (hcard : Fintype.card I = 262144)
    (row : ComparisonSpace 179740 48669 5 x u v) (hrow : row.1 ≠ 0)
    (hdet : ∀ other : ComparisonSpace 179740 48669 67471 x u v,
      coefficientDeterminant row.1 other.1 = 0)
    (seedCount B : ℕ)
    (honeCase : (let r := symbolicRow row.1
      (r.first ≠ 0 ∧ r.second = 0) ∨ (r.first = 0 ∧ r.second ≠ 0)) → seedCount ≤ B)
    (hbothCase : ∀ (q : SymbolicRow (SeedRing K)) (m : SeedCoefficients K),
      q.first ≠ 0 → q.second ≠ 0 → m ≠ 0 → IsPrimitiveRow q → RowFactors q (rankRow row.1) m →
      primitiveExcess 131071 q + (primitiveBadNodes x u v q).card ≤ 33735 → seedCount ≤ B) :
    seedCount ≤ B := by
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

/-- Localize the two-row dichotomy and primitive discard before asking for a
bound, so that hypotheses about the original assigned supports survive. -/
private theorem local_rank_cut (x : I ↪ K) (σ : K →+* K) (hx : ∀ i, σ (x i)=x i)
    (hs : ∀ z, σ z=z^prime) (card : Fintype.card I=262144)
    (U : Received K I) (S : Finset K) (P : SelectionMap K) (sel : Selection x U S P)
    {B : ℕ} (budget_le : budget ≤ B)
    (cut : ∀ T ⊆ S, ∀ q, RetainedComparison x σ U T P q →
      T.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤B) : S.card≤B := by
  let u := conjugateWord σ (U 0)
  let v := conjugateWord σ (U 1)
  obtain ⟨row,nz⟩ := exists_nonzero_comparison_row 179740 48669 5 82404 x u v card (by decide +kernel)
  by_cases mixed : ∃ other : Rows x σ U 67471, coefficientDeterminant row.1 other.1 ≠ 0
  · obtain ⟨other,det⟩ := mixed
    exact (K6969Global.mixed x σ hx hs card U row other det S P sel).trans budget_le
  apply card_le_from_primitive_cases x u v card row nz
    (fun other => not_ne_iff.mp (fun h => mixed ⟨other,h⟩)) S.card B
    (fun hone => (one_sided_rows_le_seed_budget x σ hx hs card U row hone S P sel).trans budget_le)
  intro q m hf ht hm prim factor cap
  obtain ⟨T,sub,count,good⟩ := K6969Discard.retain_primitive_rows
    (A := 179740) (a := 48669) (w := 131071) (p := prime)
    x σ hx hs (by decide) U (by decide) (by decide) row q m hm
    (Or.inl hf) factor S (agreementSet x U P) P
    sel.degree_le sel.agreement (fun _ _ _ hi => eval_eq_of_mem_agreementSet hi)
  have rem := cut T sub q ⟨selection_of_subset sel sub,hf,ht,prim,primitive_x_degree_caps row.1 q m hm factor,
    primitive_seed_degree_caps row.1 q m hm factor,cap,good⟩
  change primitiveExcess 131071 q + (badNodes x σ U q).card ≤ 33735 at cap
  calc
    S.card ≤ T.card + ((badNodes x σ U q).card+1)*(6*(prime+1)) := count
    _ ≤ T.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1) := by
      apply Nat.add_le_add_left
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ B := rem

private theorem local_retained [CharP K 2130706433] (x : I ↪ K) (σ : K ≃+* K)
    (hx : ∀ i, σ (x i)=x i) (hs : ∀ z, σ z=z^prime) (hcard : Fintype.card I=262144)
    (U : Received K I) (S : Finset K) (P : SelectionMap K) (q : SymbolicRow (SeedRing K))
    (h : RetainedComparison x σ.toRingHom U S P q)
    (normal : (∀ keys, (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0) →
      NormalForm q 131071 (primitiveExcess 131071 q) →
      S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget) :
      S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget := by
  classical
  let δ := primitiveExcess 131071 q
  let c := combinedDegree q
  let ag := agreementSet x U P
  have hδ : δ≤33735 := (Nat.le_add_right _ _).trans h.excess_bad
  have hβ₀ : q.beta.natDegree-131071≤δ := le_max_left _ _
  have hβ : q.beta.natDegree≤131071+δ := by omega
  have ha : q.first.natDegree≤δ := (le_max_left _ _).trans (le_max_right _ _)
  have hb : q.second.natDegree≤δ := (le_max_right _ _).trans (le_max_right _ _)
  by_cases ord : 2≤c ∧ K6969OrdinaryLarge.minExcess c≤δ
  · exact (K6969OrdinaryLarge.seed_count x σ.toRingHom hx hs hcard U S P q h.selection
      h.first_ne h.second_ne h.primitive hδ h.good ord.2 ord.1 (combined_degree_le_twelve h)).trans (by decide +kernel)
  have hr : c≤1 ∨ δ<K6969OrdinaryLarge.minExcess c := by omega
  by_cases allzero : ∀ keys, (Koala6831RankFour.matrix q keys δ).det=0
  · apply normal allzero
    by_cases hc : c≤1
    · exact Classical.choice (FrontierGeometry.linear_normal_form q 131071 δ h.first_ne h.second_ne ha hb hβ hc)
    · have hd : δ≤16222 := by
        have hl : δ<K6969OrdinaryLarge.minExcess c := hr.resolve_left hc
        unfold K6969OrdinaryLarge.minExcess at hl
        split at hl <;> omega
      exact Classical.choice (small_normal_form hcard h hd allzero)
  push_neg at allzero
  obtain ⟨keys,hn⟩ := allzero
  have hc : ¬ c≤1 := fun hc => hn (Koala6831Separated.all_minors_singular_of_total_weight_le_one
    q h.first_ne h.second_ne δ hc keys)
  have hd := hr.resolve_left hc
  have good (g) (hg:g∈S) (i) (hi:i∈ag g) :=
    Koala6831BenchmarkResidual.good_node_identity (fun hi' => (Finset.disjoint_left.mp (h.good g hg).2) hi hi')
  have hv (g) (_hg:g∈S) (i) (hi:i∈ag g) := eval_eq_of_mem_agreementSet hi
  have hp (F G : Polynomial K) (hF:F.natDegree≤131071) (hG:G.natDegree≤131071) :
      (S.filter (fun g => P g=F+Polynomial.C g*G)).card≤82404+1 := by
    exact h.selection.pencil F G hF hG
  have hprice : S.card≤82405 := by
    by_cases hsmall : c≤2
    · have hδ' : δ≤16222 := by simpa [K6969OrdinaryLarge.minExcess,hsmall,Nat.lt_succ_iff] using hd
      exact _root_.Frontier6969.Extract.rank_three_actual σ x hx S ag P (U 0) (U 1) q 131071 δ 82404
        ha hb hβ h.first_ne h.second_ne hsmall keys hn good h.selection.degree_le
        (fun g hg => Nat.lt_of_lt_of_le (by omega : 131071+3*δ<179740) (h.selection.agreement g hg)) hv hp
    · have hδ' : δ≤12167 := by simpa [K6969OrdinaryLarge.minExcess,hsmall,Nat.lt_succ_iff] using hd
      let w := fun i : I => ![U 0 i,U 1 i,σ (U 0 i),σ (U 1 i)]
      have hcols (j : Fin 4) : (Koala6831RankFour.columns q j).natDegree≤δ := by
        fin_cases j
        · exact ha
        · exact (Polynomial.natDegree_C_mul_le _ _).trans ha
        · exact hb
        · exact (Polynomial.natDegree_C_mul_le _ _).trans hb
      exact Koala6831CoefficientSystem.card_le_of_nonsingular_coefficients x S ag P
        (Koala6831RankFour.columns q) (-q.beta) keys w 131071 δ 82404 hn hcols (by simpa using hβ)
        h.selection.degree_le
        (fun g hg => Nat.lt_of_lt_of_le (by omega : 131071+4*δ<179740) (h.selection.agreement g hg))
        (fun g hg i hi => Koala6831RankFour.equation_of_good_node q (x i) (w i) (good g hg i hi))
        hv hp
  change S.card+(33735-δ+1)*6*(prime+1)≤budget
  unfold budget prime
  omega


private theorem assigned_subset (x : I ↪ K) (U : Received K I) (A : K → Finset I)
    (P : SelectionMap K) (g : K)
    (fit : ∀ i∈A g,(P g).eval (x i)=U 0 i+g*U 1 i) : A g ⊆ agreementSet x U P g := by
  intro i hi
  unfold agreementSet
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fit i hi⟩

private theorem selection_of_bad (x : I ↪ K) (card : Fintype.card I=262144) (U : Received K I)
    (E : Finset K) (A : K → Finset I) (P : SelectionMap K) (deg : ∀g∈E,(P g).natDegree≤131071)
    (enough : ∀g∈E,179740≤(A g).card)
    (fit : ∀g∈E,∀i∈A g,(P g).eval (x i)=U 0 i+g*U 1 i)
    (bad : Bad x U E P) : Selection x U E P := by
  classical
  have near (g) (hg:g∈E) := (enough g hg).trans (Finset.card_le_card (assigned_subset x U A P g (fit g hg)))
  refine ⟨deg,near,?_⟩
  intro V W hV hW
  by_contra! many
  let T := RCN050.pencilSeeds E P V W
  have sub : T⊆E := Finset.filter_subset _ _
  let pair : Fin 2 → I → K := ![fun i => V.eval (x i),fun i => W.eval (x i)]
  have big : 82404+1<T.card := many
  obtain ⟨g,hg,ag⟩ := exists_common_affine_set U pair T (agreementSet x U P) 82404 big (by
    intro g hg
    rw [card]
    exact near g (sub hg)) (by
    intro g hg i hi
    have eq : P g=V+Polynomial.C g*W := (Finset.mem_filter.mp hg).2
    have v := eval_eq_of_mem_agreementSet (x:=x) (received:=U) (selected:=P) hi
    rw [eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] at v
    exact v.symm)
  exact bad g (sub hg) ⟨V,W,hV,hW,fun i hi => ⟨(ag i hi).1.symm,(ag i hi).2.symm⟩⟩

private theorem exact_pencil (x : I ↪ K) (card : Fintype.card I=262144) (U : Received K I)
    (E : Finset K) (A : K → Finset I) (P : SelectionMap K) (deg : ∀g∈E,(P g).natDegree≤131071)
    (e : ℕ) (enough : ∀g∈E,262144-e≤(A g).card)
    (fit : ∀g∈E,∀i∈A g,(P g).eval (x i)=U 0 i+g*U 1 i)
    (bad : Bad x U E P) : ∀ V W : Polynomial K, V.natDegree≤131071 → W.natDegree≤131071 → (RCN050.pencilSeeds E P V W).card≤e+1 := by
  classical
  have near (g) (hg:g∈E) := (enough g hg).trans (Finset.card_le_card (assigned_subset x U A P g (fit g hg)))
  intro V W hV hW
  by_contra! many
  let T := RCN050.pencilSeeds E P V W
  have sub : T⊆E := Finset.filter_subset _ _
  let pair : Fin 2 → I → K := ![fun i => V.eval (x i),fun i => W.eval (x i)]
  have big : e+1<T.card := many
  obtain ⟨g,hg,ag⟩ := exists_common_affine_set U pair T (agreementSet x U P) e big (by
    intro g hg
    rw [card]
    exact near g (sub hg)) (by
    intro g hg i hi
    have eq : P g=V+Polynomial.C g*W := (Finset.mem_filter.mp hg).2
    have v := eval_eq_of_mem_agreementSet (x:=x) (received:=U) (selected:=P) hi
    rw [eq,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C] at v
    exact v.symm)
  exact bad g (sub hg) ⟨V,W,hV,hW,fun i hi => ⟨(ag i hi).1.symm,(ag i hi).2.symm⟩⟩

private theorem local_normal (U : Received F IRSProfile.Index) (S : Finset F)
    (P : SelectionMap F) (q : SymbolicRow (SeedRing F)) (h : RetainedComparison Dmn σ U S P q)
    (bad : Bad Dmn U S P) (singular : ∀ keys, (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0)
    (N : NormalForm q 131071 (primitiveExcess 131071 q))
    (rem : ∀ (short : primitiveExcess 131071 q < 12137) (dc : combinedDegree q ≤ 2),
      (pairDegree N.A+pairDegree N.B+472<primitiveExcess 131071 q ∨
        (N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0 ∧ N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0 ∧ IsCoprime N.d₀ N.d₁)) →
      S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget) :
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget := by
  let hchar := Koala6831BenchmarkField.characteristic
  by_cases hshort : primitiveExcess 131071 q < 12137
  · by_cases d : primitiveExcess 131071 q ≤ pairDegree N.A + pairDegree N.B + 472
    · by_cases left : N.d₀ ∣ N.A 0*N.C 1-N.A 1*N.C 0
      · by_cases right : N.d₁ ∣ N.B 0*N.D 1-N.B 1*N.D 0
        · by_cases cp : IsCoprime N.d₀ N.d₁
          · exact rem hshort (normal_degree N) (Or.inr ⟨left,right,cp⟩)
          · exact moving_determinant_class Dmn σ Koala6831BenchmarkField.frobenius_apply U S P q h N (Or.inr (Or.inr cp)) d
        · exact moving_determinant_class Dmn σ Koala6831BenchmarkField.frobenius_apply U S P q h N (Or.inr (Or.inl right)) d
      · exact moving_determinant_class Dmn σ Koala6831BenchmarkField.frobenius_apply U S P q h N (Or.inl left) d
    · exact rem hshort (normal_degree N) (Or.inl (lt_of_not_ge d))
  have hd : primitiveExcess 131071 q≤33735 := (Nat.le_add_right _ _).trans h.excess_bad
  have bound := Koala6831BenchmarkResidual.separated_retained_6969 Koala6831BenchmarkField.domain_fixed
    Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index h.primitive h.first_ne h.second_ne
    (by omega) hd N h.good h.selection.degree_le h.selection.agreement h.selection.pencil
  unfold budget prime
  omega

theorem classify (U : Received F IRSProfile.Index) (S : Finset F) (P : SelectionMap F)
    (q : SymbolicRow (Seeds F)) (h : RetainedComparison Dmn σ U S P q) (bad : Bad Dmn U S P) :
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget ∨
    ∃ N : NormalForm q 131071 (primitiveExcess 131071 q), Difficult U S P q N := by
  classical
  by_cases form : ∃ N : NormalForm q 131071 (primitiveExcess 131071 q), Difficult U S P q N
  · exact Or.inr form
  left
  let noForm := form
  letI := Koala6831BenchmarkField.characteristic
  apply local_retained Dmn frobenius Koala6831BenchmarkField.domain_fixed Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index U S P q h
  intro rank N
  apply local_normal U S P q h bad rank N
  intro short dc old
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
  · exact (noForm ⟨N,⟨h,bad,short,rank,dc,gap,aligned,ker,low,yes,eff,vis,pair,mix,lin⟩⟩).elim
  push Not at lin
  have n := (linear_or_small U S P q h bad lin.1).resolve_left lin.2
  unfold budget prime
  omega

def At (A B : ℕ) : Prop :=
  ∀ (U : Received F IRSProfile.Index) (S : Finset F) (P : SelectionMap F) (q : SymbolicRow (Seeds F))
    (N : NormalForm q 131071 (primitiveExcess 131071 q)), Difficult U S P q N →
    (∀ g∈S, A≤(agreementSet Dmn U P g).card) →
    (∀ V W : Polynomial F, V.natDegree≤131071 → W.natDegree≤131071 →
      (RCN050.pencilSeeds S P V W).card≤262144-A+1) →
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤B

theorem given_of_at {r : ℝ≥0} {A B : ℕ} (minA : 179740 ≤ A) (maxA : A≤262144)
    (old_le : budget≤B) (cell : (r:ℝ)*262144 < ((262144-A+1 : ℕ):ℝ))
    (rem : At A B) : AffineLineGivenSetsBound IRSProfile.baseCode (r:ℝ) B := by
  classical
  intro U E J large size projected
  obtain ⟨P,deg,fit⟩ := RCN050.exists_selected_polynomials Dmn 131071 U E J projected
  have enough (g:F) (hg:g∈E) : A≤(J g).card := by
    have s := size g hg
    simp only [IRSProfile.card_index, Nat.cast_ofNat] at s
    have cast : (((262144-A+1:ℕ):ℝ))=262144-(A:ℝ)+1 := by rw [Nat.cast_add,Nat.cast_sub maxA]; norm_num
    rw [cast] at cell
    have hh : (A:ℝ)<((J g).card:ℝ)+1 := by linarith only [s,cell]
    have hhNat : A < (J g).card+1 := by exact_mod_cast hh
    omega
  have incl (g:F) (hg:g∈E) : J g ⊆ agreementSet Dmn U P g := assigned_subset Dmn U J P g (fit g hg)
  by_contra no
  have bad : Bad Dmn U E P := by
    intro g hg
    rintro ⟨V,W,hV,hW,agree⟩
    apply no
    refine ⟨g,hg,?_⟩
    have mem (j : Fin 2) (Q : Polynomial F) (hq : Q.natDegree≤131071)
        (ag : ∀ i∈J g, Q.eval (Dmn i)=U j i) :
        LinearCode.projectedWord (U j) (J g) ∈ LinearCode.projectedCodeSubmod IRSProfile.baseCode (J g) := by
      refine ⟨ReedSolomon.evalOnPoints Dmn Q, ReedSolomon.evalOnPoints_mem_code_of_degree_lt
        (RCN050.degree_lt_succ_of_natDegree_le Q 131071 hq),?_⟩
      funext i
      exact ag i.val i.property
    intro j
    fin_cases j
    · exact mem _ V hV (fun i hi => (agree i (incl g hg hi)).1)
    · exact mem _ W hW (fun i hi => (agree i (incl g hg hi)).2)
  have base := selection_of_bad Dmn IRSProfile.card_index U E J P deg (fun g hg => minA.trans (enough g hg)) fit bad
  have cap := local_rank_cut Dmn σ Koala6831BenchmarkField.domain_fixed Koala6831BenchmarkField.frobenius_apply IRSProfile.card_index U E P base old_le (by
    intro T sub q h
    have no : Bad Dmn U T P := fun g hg => bad g (sub hg)
    rcases classify U T P q h no with priced | ⟨N,form⟩
    · exact priced.trans old_le
    apply rem U T P q N form (fun g hg => (enough g (sub hg)).trans (Finset.card_le_card (incl g (sub hg))))
    exact exact_pencil Dmn IRSProfile.card_index U T J P (fun g hg => deg g (sub hg)) (262144-A) (fun g hg => by simpa [Nat.sub_sub_self maxA] using enough g (sub hg)) (fun g hg => fit g (sub hg)) no)
  exact (not_lt_of_ge cap) large
#print axioms classify
#print axioms given_of_at
end
end ProximityPrize.SubmissionLower.Intermediate
