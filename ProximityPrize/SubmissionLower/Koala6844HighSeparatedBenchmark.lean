import ProximityPrize.SubmissionLower.Koala6844HighSeparatedPrimitive


namespace ProximityPrize.SubmissionLower.Koala6844HighSeparated

open Koala6844Comparison Koala6844HighOrdinary
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000

variable {K I : Type} [Field K] [Fintype I]

private abbrev Received (K I : Type) := Fin 2 → I → K

private def agreementSet (x : I ↪ K) (received : Received K I) (selected : K → Polynomial K)
    (g : K) : Finset I :=
  @Finset.filter _ (fun i => (selected g).eval (x i) =
    received 0 i + g * received 1 i) (fun _ => Classical.propDecidable _) Finset.univ

private theorem eval_eq_of_mem_agreementSet
    {x : I ↪ K} {received : Received K I} {selected : K → Polynomial K} {g : K} {i : I}
    (hi : i ∈ agreementSet x received selected g) :
    (selected g).eval (x i) = received 0 i + g * received 1 i :=
  (Finset.mem_filter.mp hi).2

private theorem exists_retained_carrier
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ 2130706433) (hcard : Fintype.card I = 262144)
    (U : Received K I) (retained : Finset K) (P : K → Polynomial K)
    (hdegree : ∀ g ∈ retained, (P g).natDegree ≤ 131071)
    (hnear : ∀ g ∈ retained, 180957 ≤ (agreementSet x U P g).card)
    (q : SymbolicRow (SeedRing K)) (hprim : IsPrimitiveRow q)
    (hf : q.first ≠ 0) (hs : q.second ≠ 0)
    (hδ : 9800 ≤ primitiveExcess 131071 q) (hδ' : primitiveExcess 131071 q ≤ 31614)
    (normal : Koala6844Separation.NormalForm q 131071 (primitiveExcess 131071 q))
    (hkeep : ∀ g ∈ retained, primitiveSelected σ 2130706433 q P g = 0 ∧
      Disjoint (agreementSet x U P g)
        (primitiveBadNodes x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)) q)) :
    ∃ G : Carrier K, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧
        d 0 + 131071 * d 1 ≤ 16 * 180957 - 1 + 22 * primitiveExcess 131071 q ∧
        d 0 + 131071 * d 1 < 2130706433) ∧
      ∀ g ∈ retained, Koala6844HighOrdinaryIntrinsic.graphSpecialize (P g) g (g ^ 2130706433) G = 0 := by
  classical
  let agree := agreementSet x U P
  let u := conjugateWord σ (U 0)
  let v := conjugateWord σ (U 1)
  let bad := primitiveBadNodes x u v q
  let Good := { i : I // i ∉ bad }
  let goodX : Good ↪ K := (Function.Embedding.subtype (· ∉ bad)).trans x
  let agreement (g : ↥retained) := (agree g.1).subtype (· ∉ bad)
  have good_count : Fintype.card Good ≤ 262144 := by
    rw [← hcard]
    exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have good_node (i : Good) :
      q.atNode (MvPolynomial.C (goodX i))
        (MvPolynomial.C (U 0 i.1) + MvPolynomial.X 0 * MvPolynomial.C (U 1 i.1))
        (MvPolynomial.C (σ (U 0 i.1)) + MvPolynomial.X 1 * MvPolynomial.C (σ (U 1 i.1))) = 0 := by
    by_contra hn
    apply i.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change q.atNode (MvPolynomial.C (x i.1)) (affineSeedWord u v 0 i.1)
      (affineSeedWord u v 1 i.1) ≠ 0
    have heq : q.atNode (MvPolynomial.C (x i.1))
        (MvPolynomial.C (U 0 i.1) + MvPolynomial.X 0 * MvPolynomial.C (U 1 i.1))
        (MvPolynomial.C (σ (U 0 i.1)) + MvPolynomial.X 1 * MvPolynomial.C (σ (U 1 i.1))) ≠ 0 := hn
    simpa only [affineSeedWord, u, v, conjugateWord, zero_ne_one, one_ne_zero,
      ite_true, ite_false] using heq
  have agreeing_count (g : ↥retained) : 180957 ≤ (agreement g).card := by
    have havoid := Finset.disjoint_left.mp (hkeep g.1 g.2).2
    have eq : (agree g.1).filter (· ∉ bad) = agree g.1 :=
      Finset.filter_true_of_mem (fun i hi hb => havoid hi hb)
    change 180957 ≤ ((agree g.1).subtype (· ∉ bad)).card
    rw [Finset.card_subtype, eq]
    exact hnear g.1 g.2
  have natDegree (g : ↥retained) : (P g.1).natDegree ≤ 131071 := hdegree g.1 g.2
  have agrees₀ (g : ↥retained) (i : Good) (hi : i ∈ agreement g) :
      (P g.1).eval (goodX i) = U 0 i.1 + g.1 * U 1 i.1 :=
    eval_eq_of_mem_agreementSet (Finset.mem_subtype.mp hi)
  have agrees₁ (g : ↥retained) (i : Good) (hi : i ∈ agreement g) :
      ((P g.1).map σ).eval (goodX i) = σ (U 0 i.1) + g.1 ^ 2130706433 * σ (U 1 i.1) := by
    have h : ((P g.1).map σ).eval (σ (x i.1)) = σ ((P g.1).eval (x i.1)) :=
      Polynomial.eval_map_apply σ (x i.1)
    rw [hfixed i.1] at h
    have h_agree := agrees₀ g i hi
    change (P g.1).eval (x i.1) = _ at h_agree
    change ((P g.1).map σ).eval (x i.1) = _
    rw [h, h_agree, map_add, map_mul, hpow g.1]
  obtain ⟨G, nonzero, caps, graph⟩ := exists_long_separated_carrier_of_primitive goodX
    (fun i => U 0 i.1) (fun i => U 1 i.1) (fun i => σ (U 0 i.1)) (fun i => σ (U 1 i.1))
    good_count q hprim hf hs hδ hδ' normal good_node σ 2130706433 P Subtype.val agreement
    natDegree agreeing_count agrees₀ agrees₁ (fun g => (hkeep g.1 g.2).1)
  exact ⟨G, nonzero, caps, fun g hg => graph ⟨g, hg⟩⟩

end

open ProximityPrize.Benchmark
open Koala6844BenchmarkCases Koala6844BenchmarkField Koala6844BenchmarkRetention

theorem exists_benchmark_carrier
    (received : ReceivedWords) (retained : Finset IRSProfile.Field)
    (selected : IRSProfile.Field → Polynomial IRSProfile.Field)
    (q : SymbolicRow (SeedRing IRSProfile.Field))
    (data : RetainedComparison received retained selected q)
    (high : 9800 ≤ primitiveExcess 131071 q)
    (normal : Koala6844Separation.NormalForm q 131071 (primitiveExcess 131071 q)) :
    ∃ G : Carrier IRSProfile.Field, G ≠ 0 ∧
      (∀ d ∈ G.support, d 1 ≤ 22 ∧ d 1 + d 2 ≤ 200 ∧ d 3 ≤ 162 ∧
        d 0 + 131071 * d 1 ≤ 16 * 180957 - 1 + 22 * primitiveExcess 131071 q ∧
        d 0 + 131071 * d 1 < 2130706433) ∧
      ∀ g ∈ retained, Koala6844HighOrdinaryIntrinsic.graphSpecialize
        (selected g) g (g ^ 2130706433) G = 0 := by
  classical
  have upper : primitiveExcess 131071 q ≤ 31614 :=
    (Nat.le_add_right _ _).trans data.excess_bad
  exact exists_retained_carrier IRSProfile.domain frobenius.toRingHom domain_fixed frobenius_apply
    IRSProfile.card_index received retained selected data.selection.degree_le data.selection.agreement
    q data.primitive data.first_ne data.second_ne high upper normal data.good

end ProximityPrize.SubmissionLower.Koala6844HighSeparated
