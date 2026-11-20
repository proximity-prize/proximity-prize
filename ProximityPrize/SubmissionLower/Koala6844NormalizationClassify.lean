import ProximityPrize.SubmissionLower.Koala6844NormalizationSeparation


namespace ProximityPrize.SubmissionLower.Koala6844Normalization

open ProximityPrize.Benchmark
open Koala6844BenchmarkField (frobenius)
open Koala6844BenchmarkCases (ReceivedWords)
open Koala6844BenchmarkRetention (RetainedComparison badNodes)
open Koala6844Comparison (SeedRing SymbolicRow primitiveExcess seedNode affineSeedWord)
open Koala6844Separation (NormalForm)
open scoped Classical Matrix

noncomputable section
set_option maxHeartbeats 650000
set_option maxRecDepth 12000

private def fitsNode (received : ReceivedWords) (q : SymbolicRow (SeedRing IRSProfile.Field))
    (i : IRSProfile.Index) : Prop :=
  q.atNode (MvPolynomial.C (IRSProfile.domain i))
    (MvPolynomial.C (received 0 i) + MvPolynomial.X 0 * MvPolynomial.C (received 1 i))
    (MvPolynomial.C (frobenius (received 0 i)) +
      MvPolynomial.X 1 * MvPolynomial.C (frobenius (received 1 i))) = 0

def goodNodes (received : ReceivedWords) (q : SymbolicRow (SeedRing IRSProfile.Field)) :
    Finset IRSProfile.Index :=
  @Finset.filter _ (fitsNode received q) (fun _ => Classical.propDecidable _) Finset.univ

private def receivedCoordinates (received : ReceivedWords) (i : IRSProfile.Index) :
    Fin 4 → IRSProfile.Field :=
  ![received 0 i, received 1 i, frobenius (received 0 i), frobenius (received 1 i)]

theorem good_node_identity {received : ReceivedWords} {q : SymbolicRow (SeedRing IRSProfile.Field)}
    {i : IRSProfile.Index} (hi : i ∈ goodNodes received q) :
    q.atNode (MvPolynomial.C (IRSProfile.domain i))
      (MvPolynomial.C (received 0 i) + MvPolynomial.X 0 * MvPolynomial.C (received 1 i))
      (MvPolynomial.C (frobenius (received 0 i)) +
        MvPolynomial.X 1 * MvPolynomial.C (frobenius (received 1 i))) = 0 :=
  (Finset.mem_filter.mp hi).2

theorem goodNodes_eq_sdiff {received : ReceivedWords} {q : SymbolicRow (SeedRing IRSProfile.Field)} :
    goodNodes received q = Finset.univ \ badNodes received q := by
  classical
  ext i
  simp only [goodNodes, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  change fitsNode received q i ↔ _ 
  unfold badNodes Koala6844Comparison.primitiveBadNodes
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_ne_iff]
  rfl

theorem goodNodes_card {received : ReceivedWords} {q : SymbolicRow (SeedRing IRSProfile.Field)} :
    (goodNodes received q).card = 262144 - (badNodes received q).card := by
  rw [goodNodes_eq_sdiff, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    IRSProfile.card_index]

theorem normal_form_of_retained_singular
    {received : ReceivedWords} {retained : Finset IRSProfile.Field}
    {selected : IRSProfile.Field → Polynomial IRSProfile.Field}
    {q : SymbolicRow (SeedRing IRSProfile.Field)}
    (h : RetainedComparison received retained selected q)
    (hsingular : ∀ keys : Fin 4 → Koala6844CoefficientSystem.SeedMonomial,
      (Koala6844RankFour.matrix q keys (primitiveExcess 131071 q)).det = 0) :
    Nonempty (NormalForm q 131071 (primitiveExcess 131071 q)) := by
  let δ := primitiveExcess 131071 q
  have hδz : δ + (badNodes received q).card ≤ 31614 := h.excess_bad
  have hnodes := goodNodes_card (received := received) (q := q)
  have hnodesLarge : 131071 + 4 * δ < (goodNodes received q).card := by omega
  have hbetaExcess : q.beta.natDegree - 131071 ≤ δ := le_max_left _ _
  have hβ : q.beta.natDegree ≤ 131071 + δ := by omega
  have hfirst : q.first.natDegree ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hsecond : q.second.natDegree ≤ δ := (le_max_right _ _).trans (le_max_right _ _)
  refine Koala6844Separation.normalForm_of_singular IRSProfile.domain (goodNodes received q)
    q (receivedCoordinates received) 131071 δ h.first_ne h.second_ne hfirst hsecond hβ
    (by omega) hnodesLarge ?_ hsingular h.primitive
  intro i hi
  simpa [receivedCoordinates] using good_node_identity hi

end

end ProximityPrize.SubmissionLower.Koala6844Normalization

