import ProximityPrize.SubmissionLower.Koala6831BenchmarkGeometry
import ProximityPrize.SubmissionLower.Koala6831OrdinaryTestAdapter
import ProximityPrize.SubmissionLower.Koala6831SeparatedDegreeOne
import ProximityPrize.SubmissionLower.Koala6831SeparatedPrimitive

namespace ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual

open ProximityPrize.Benchmark
open Koala6831BenchmarkField (prime frobenius domain_fixed frobenius_apply)
open Koala6831BenchmarkPrimitive Koala6831BenchmarkRetention Koala6831BenchmarkGeometry
open Koala6831Comparison Koala6831Ordinary Koala6831Quotient
open Koala6831Separation (NormalForm)
open scoped Classical Matrix

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000

variable {K I : Type} [Field K] [Fintype I]

abbrev combinedDegree (q : SymbolicRow (SeedRing K)) : ℕ :=
  weightDegree totalWeights (primitiveRowLift q)

theorem combined_degree_le_ten
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (h : RetainedComparison x σ received retained selected q) :
    combinedDegree q ≤ 10 := by
  have hβ := liftedCoefficient_total_weight_le q.beta 5 5
    (fun j => (h.seedDegree j).1.1) (fun j => (h.seedDegree j).1.2)
  have ha := liftedCoefficient_total_weight_le q.first 4 5
    (fun j => (h.seedDegree j).2.1.1) (fun j => (h.seedDegree j).2.1.2)
  have hb := liftedCoefficient_total_weight_le q.second 5 4
    (fun j => (h.seedDegree j).2.2.1) (fun j => (h.seedDegree j).2.2.2)
  have ha' : weightDegree totalWeights
      (retainCarrier (carrierOfSeedCoefficients q.first) * MvPolynomial.X 1) ≤ (4 + 5) + 1 :=
    (weight_mul_le _ _ _).trans (by
      rw [weight_X]
      exact Nat.add_le_add ha (show totalWeights 1 ≤ 1 by decide))
  have hb' : weightDegree totalWeights
      (retainCarrier (carrierOfSeedCoefficients q.second) * MvPolynomial.X 2) ≤ (5 + 4) + 1 :=
    (weight_mul_le _ _ _).trans (by
      rw [weight_X]
      exact Nat.add_le_add hb (show totalWeights 2 ≤ 1 by decide))
  change weightDegree totalWeights (primitiveRowLift q) ≤ 10
  rw [primitiveRowLift_weight_max]
  exact max_le (max_le hβ ha') hb'

private def coordinates (σ : K →+* K) (received : Received K I) (i : I) : Fin 4 → K :=
  ![received 0 i, received 1 i, σ (received 0 i), σ (received 1 i)]

theorem good_node_identity {x : I ↪ K} {σ : K →+* K}
    {received : Received K I} {q : SymbolicRow (SeedRing K)} {i : I}
    (hi : i ∉ badNodes x σ received q) :
    q.atNode (MvPolynomial.C (x i))
      (MvPolynomial.C (received 0 i) + MvPolynomial.X 0 * MvPolynomial.C (received 1 i))
      (MvPolynomial.C (σ (received 0 i)) + MvPolynomial.X 1 * MvPolynomial.C (σ (received 1 i))) = 0 := by
  have hzero : q.atNode (seedNode x i)
      (affineSeedWord (conjugateWord σ (received 0)) (conjugateWord σ (received 1)) 0 i)
      (affineSeedWord (conjugateWord σ (received 0)) (conjugateWord σ (received 1)) 1 i) = 0 := by
    by_contra hnonzero
    apply hi
    unfold badNodes primitiveBadNodes
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnonzero⟩
  simpa [seedNode, affineSeedWord, conjugateWord] using hzero

theorem normal_form_of_retained_singular
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (hcard : Fintype.card I = 262144)
    (h : RetainedComparison x σ received retained selected q)
    (hsingular : ∀ keys : Fin 4 → Koala6831CoefficientSystem.SeedMonomial,
      (Koala6831RankFour.matrix q keys (primitiveExcess 131071 q)).det = 0) :
    Nonempty (NormalForm q 131071 (primitiveExcess 131071 q)) := by
  let δ := primitiveExcess 131071 q
  let nodes := (Finset.univ : Finset I) \ badNodes x σ received q
  have hδz : δ + (badNodes x σ received q).card ≤ 31357 := h.excess_bad
  have hnodes : nodes.card = 262144 - (badNodes x σ received q).card := by
    unfold nodes
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard]
  have hnodesLarge : 131071 + 4 * δ < nodes.card := by omega
  have hbetaExcess : q.beta.natDegree - 131071 ≤ δ := le_max_left _ _
  have hβ : q.beta.natDegree ≤ 131071 + δ := by omega
  have hfirst : q.first.natDegree ≤ δ := (le_max_left _ _).trans (le_max_right _ _)
  have hsecond : q.second.natDegree ≤ δ := (le_max_right _ _).trans (le_max_right _ _)
  refine Koala6831Separation.normalForm_of_singular x nodes q (coordinates σ received) 131071 δ
    h.first_ne h.second_ne hfirst hsecond hβ (by omega) hnodesLarge ?_ hsingular h.primitive
  intro i hi
  have hnotBad : i ∉ badNodes x σ received q := (Finset.mem_sdiff.mp hi).2
  simpa [coordinates] using good_node_identity hnotBad

structure LongCarrier (q : SymbolicRow (SeedRing K)) (retained : Finset K)
    (selected : SelectionMap K) where
  polynomial : Carrier K
  nonzero : polynomial ≠ 0
  support : ∀ d ∈ polynomial.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 165 ∧
    d 0 + 131071 * d 1 ≤ 16 * 181078 - 1 + 22 * primitiveExcess 131071 q ∧
    d 0 + 131071 * d 1 < prime
  vanishes : ∀ g ∈ retained,
    Koala6831Intrinsic.graphSpecialize (selected g) g (g ^ prime) polynomial = 0

theorem long_carrier_of_retained
    {x : I ↪ K} {σ : K →+* K} {received : Received K I}
    {retained : Finset K} {selected : SelectionMap K}
    {q : SymbolicRow (SeedRing K)}
    (hfixed : ∀ i, σ (x i) = x i) (hpow : ∀ g : K, σ g = g ^ prime)
    (hcard : Fintype.card I = 262144)
    (h : RetainedComparison x σ received retained selected q)
    (hlong : 9554 ≤ primitiveExcess 131071 q) (hsmall : primitiveExcess 131071 q ≤ 31357)
    (N : NormalForm q 131071 (primitiveExcess 131071 q)) :
    Nonempty (LongCarrier q retained selected) := by
  let bad := badNodes x σ received q
  let Good := {i : I // i ∉ bad}
  let goodX : Good ↪ K := (Function.Embedding.subtype (· ∉ bad)).trans x
  let agree (g : ↥retained) : Finset Good :=
    (agreementSet x received selected g.1).subtype (· ∉ bad)
  have hgoodCard : Fintype.card Good ≤ 262144 := by
    rw [← hcard]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hgood (i : Good) :
      q.atNode (MvPolynomial.C (goodX i))
        (MvPolynomial.C (received 0 i.1) + MvPolynomial.X 0 * MvPolynomial.C (received 1 i.1))
        (MvPolynomial.C (σ (received 0 i.1)) + MvPolynomial.X 1 * MvPolynomial.C (σ (received 1 i.1))) = 0 :=
    good_node_identity (x := x) (σ := σ) (received := received) (q := q) i.2
  have hsize (g : ↥retained) : 181078 ≤ (agree g).card := by
    have havoid := Finset.disjoint_left.mp (h.good g.1 g.2).2
    have heq : (agreementSet x received selected g.1).filter (· ∉ bad) =
        agreementSet x received selected g.1 :=
      Finset.filter_true_of_mem (fun i hi hb => havoid hi hb)
    change 181078 ≤ ((agreementSet x received selected g.1).subtype (· ∉ bad)).card
    rw [Finset.card_subtype, heq]
    exact h.selection.agreement g.1 g.2
  have h₀ (g : ↥retained) (i : Good) (hi : i ∈ agree g) :
      (selected g.1).eval (goodX i) = received 0 i.1 + g.1 * received 1 i.1 :=
    eval_eq_of_mem_agreementSet (Finset.mem_subtype.mp hi)
  have h₁ (g : ↥retained) (i : Good) (hi : i ∈ agree g) :
      ((selected g.1).map σ).eval (goodX i) = σ (received 0 i.1) + g.1 ^ prime * σ (received 1 i.1) := by
    have heval : ((selected g.1).map σ).eval (σ (x i.1)) = σ ((selected g.1).eval (x i.1)) :=
      Polynomial.eval_map_apply σ (x i.1)
    rw [hfixed i.1] at heval
    have hfit : (selected g.1).eval (x i.1) = received 0 i.1 + g.1 * received 1 i.1 := h₀ g i hi
    change ((selected g.1).map σ).eval (x i.1) = _
    rw [heval, hfit, map_add, map_mul, hpow g.1]
  obtain ⟨G, hne, hsupport, hvanish⟩ := Koala6831Separated.exists_long_separated_carrier_of_primitive
    goodX (fun i => received 0 i.1) (fun i => received 1 i.1)
    (fun i => σ (received 0 i.1)) (fun i => σ (received 1 i.1)) hgoodCard
    q h.primitive h.first_ne h.second_ne hlong hsmall N hgood σ prime selected Subtype.val agree
    (fun g => h.selection.degree_le g.1 g.2) hsize h₀ h₁ (fun g => (h.good g.1 g.2).1)
  exact ⟨⟨G, hne, hsupport, fun g hg => hvanish ⟨g, hg⟩⟩⟩

def OrdinaryRetainedCount (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ received retained selected q →
    11000 ≤ primitiveExcess 131071 q → primitiveExcess 131071 q ≤ 31357 →
    2 ≤ combinedDegree q → combinedDegree q ≤ 10 → retained.card ≤ retainedSeedBudget

def LongSeparatedRetainedCount (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ received retained selected q →
    9554 ≤ primitiveExcess 131071 q → primitiveExcess 131071 q ≤ 31357 →
    NormalForm q 131071 (primitiveExcess 131071 q) →
    LongCarrier q retained selected → retained.card ≤ retainedSeedBudget

def ShortSeparatedRetainedCount (x : I ↪ K) (σ : K →+* K) : Prop :=
  ∀ (received : Received K I) (retained : Finset K) (selected : SelectionMap K)
    (q : SymbolicRow (SeedRing K)),
    RetainedComparison x σ received retained selected q →
    primitiveExcess 131071 q ≤ 9553 →
    NormalForm q 131071 (primitiveExcess 131071 q) → retained.card ≤ retainedSeedBudget

theorem remaining_geometry_of_branches
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ prime) (hcard : Fintype.card I = 262144)
    (ordinary : OrdinaryRetainedCount x σ) (long : LongSeparatedRetainedCount x σ)
    (short : ShortSeparatedRetainedCount x σ) : RemainingGeometrySeedBound x σ := by
  intro received retained selected q h hminors
  let δ := primitiveExcess 131071 q
  let c := combinedDegree q
  have hδz : δ + (badNodes x σ received q).card ≤ 31357 := h.excess_bad
  have hδ : δ ≤ 31357 := by omega
  by_cases hOrdinary : 11000 ≤ δ ∧ 2 ≤ c
  · exact ordinary received retained selected q h hOrdinary.1 hδ hOrdinary.2
      (combined_degree_le_ten h)
  have hs : ∀ keys : Fin 4 → Koala6831CoefficientSystem.SeedMonomial,
      (Koala6831RankFour.matrix q keys δ).det = 0 := by
    by_cases hOne : c ≤ 1
    · exact Koala6831Separated.all_minors_singular_of_total_weight_le_one
        q h.first_ne h.second_ne δ hOne
    have hShort : δ ≤ 10999 := by omega
    exact hminors (show δ ≤ 12501 by omega)
  obtain ⟨N⟩ := normal_form_of_retained_singular hcard h hs
  by_cases hLong : 9554 ≤ δ
  · obtain ⟨G⟩ := long_carrier_of_retained hfixed hpow hcard h hLong hδ N
    exact long received retained selected q h hLong hδ N G
  · exact short received retained selected q h (show δ ≤ 9553 by omega) N

theorem protocolClaim_6832_of_counting_branches
    (ordinary : OrdinaryRetainedCount IRSProfile.domain frobenius.toRingHom)
    (long : LongSeparatedRetainedCount IRSProfile.domain frobenius.toRingHom)
    (short : ShortSeparatedRetainedCount IRSProfile.domain frobenius.toRingHom) :
    ProtocolClaim 6832 332050431 1073741824 :=
  protocolClaim_6832_of_geometry (remaining_geometry_of_branches IRSProfile.domain
    frobenius.toRingHom domain_fixed frobenius_apply IRSProfile.card_index ordinary long short)

private theorem benchmark_ordinary_count :
    OrdinaryRetainedCount IRSProfile.domain frobenius.toRingHom := by
  intro received retained selected q h hδ _ hc hc10
  exact Koala6831Ordinary.benchmark_ordinary_retained_le_seed_budget
    received retained selected q h hδ hc hc10

theorem protocolClaim_6832_of_separated_counts
    (long : LongSeparatedRetainedCount IRSProfile.domain frobenius.toRingHom)
    (short : ShortSeparatedRetainedCount IRSProfile.domain frobenius.toRingHom) :
    ProtocolClaim 6832 332050431 1073741824 :=
  protocolClaim_6832_of_counting_branches benchmark_ordinary_count long short

end

end ProximityPrize.SubmissionLower.Koala6831BenchmarkResidual

/- Modified for the 68.32 KoalaBear soundness construction, November 2026. -/
