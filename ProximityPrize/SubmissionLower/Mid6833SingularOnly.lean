/- Apache-2.0. Prepared for the KoalaBear 68.33 intermediate construction by Bome2017, building on Lucieno and BitWonka. Original attribution is retained below. -/
/- Apache-2.0, after Lucieno's separation and the promoted 68.32 construction.
The degree-two nonsingular slice and ordinary profiles come from this experiment. -/
import ProximityPrize.SubmissionLower.Mid6833Global
import ProximityPrize.SubmissionLower.Mid6833AffineExtraction
import ProximityPrize.SubmissionLower.Mid6833LinearNormalForm
namespace ProximityPrize.SubmissionLower.K6969Global
open Koala6831Comparison Koala6831Separation
open Koala6831BenchmarkPrimitive (Received SelectionMap agreementSet eval_eq_of_mem_agreementSet badNodes)
open Koala6831BenchmarkField (prime)
open scoped Classical BigOperators
noncomputable section
variable {K I : Type} [Field K] [Fintype I]
set_option maxRecDepth 16000
set_option maxHeartbeats 2500000
private def coordinates (σ : K →+* K) (received : Received K I) (i : I) : Fin 4 → K :=
  ![received 0 i, received 1 i, σ (received 0 i), σ (received 1 i)]

theorem small_normal_form
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (hcard : Fintype.card I = 262144)
    (h : RetainedComparison x σ received retained selected q)
    (hsmall : primitiveExcess 131071 q ≤ 16222)
    (hsingular : ∀ keys : Fin 4 → Koala6831CoefficientSystem.SeedMonomial,
      (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det = 0) :
    Nonempty (NormalForm q 131071 (primitiveExcess 131071 q)) := by
  let δ := primitiveExcess 131071 q
  let nodes := (Finset.univ : Finset I) \ badNodes x σ received q
  have hδz : δ + (badNodes x σ received q).card ≤ 33735 := h.excess_bad
  have hnodes : nodes.card = 262144 - (badNodes x σ received q).card := by
    unfold nodes
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard]
  change δ≤16222 at hsmall
  have hnodesLarge : 131071 + 4 * δ < nodes.card := by omega
  have hbetaExcess : q.beta.natDegree - 131071 ≤ δ := le_max_left _ _
  have hβ : q.beta.natDegree ≤ 131071 + δ := by omega
  have hfirst : q.first.natDegree ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hsecond : q.second.natDegree ≤ δ := (le_max_right _ _).trans (le_max_right _ _)
  refine Koala6831Separation.normalForm_of_singular x nodes q (coordinates σ received) 131071 δ
    h.first_ne h.second_ne hfirst hsecond hβ (by omega) hnodesLarge ?_ hsingular h.primitive
  intro i hi
  have hnotBad : i ∉ badNodes x σ received q := (Finset.mem_sdiff.mp hi).2
  simpa [coordinates] using Koala6831BenchmarkResidual.good_node_identity hnotBad


def SingularNormalized (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (U : Received K I) (S : Finset K) (P : SelectionMap K) (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ U S P q →
    (combinedDegree q≤1 ∨ primitiveExcess 131071 q<K6969OrdinaryLarge.minExcess (combinedDegree q)) →
    (∀ keys, (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det=0) →
    NormalForm q 131071 (primitiveExcess 131071 q) →
    S.card+(33735-primitiveExcess 131071 q+1)*6*(prime+1)≤budget

theorem selected_of_singular [CharP K 2130706433] (x : I ↪ K) (σ : K ≃+* K)
    (hx : ∀ i, σ (x i)=x i) (hs : ∀ z, σ z=z^prime) (hcard : Fintype.card I=262144)
    (gap : SingularNormalized x σ.toRingHom) : RCN050.SelectedNoLargePencilBound x 131071 82404 budget := by
  classical
  apply selected_of_retained x σ.toRingHom hx hs hcard
  intro U S P q h
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
  · apply gap U S P q h hr allzero
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
      let w := coordinates σ.toRingHom U
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

#print axioms small_normal_form
#print axioms selected_of_singular
end
end ProximityPrize.SubmissionLower.K6969Global
