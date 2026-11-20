import ProximityPrize.SubmissionLower.Koala6831OrdinaryFactorCount
import ProximityPrize.SubmissionLower.Koala6844HighOrdinaryPrimitiveCarrier


namespace ProximityPrize.SubmissionLower.Koala6844HighOrdinary

open Koala6844Comparison Koala6844HighOrdinaryQuotient Koala6831OrdinaryIncidence
open scoped Classical

noncomputable section

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 4500000

variable {K E Ω I : Type} [Field K] [Field E] [Field Ω] [Fintype I]

abbrev Received (K I : Type) := Fin 2 → I → K

def agreementSet (x : I ↪ K) (received : Received K I) (selected : K → Polynomial K)
    (g : K) : Finset I :=
  @Finset.filter _ (fun i => (selected g).eval (x i) =
    received 0 i + g * received 1 i) (fun _ => Classical.propDecidable _) Finset.univ

theorem eval_eq_of_mem_agreementSet
    {x : I ↪ K} {received : Received K I} {selected : K → Polynomial K} {g : K} {i : I}
    (hi : i ∈ agreementSet x received selected g) :
    (selected g).eval (x i) = received 0 i + g * received 1 i :=
  (Finset.mem_filter.mp hi).2

structure Selection (x : I ↪ K) (received : Received K I) (seeds : Finset K)
    (selected : K → Polynomial K) : Prop where
  degree_le : ∀ g ∈ seeds, (selected g).natDegree ≤ 131071
  agreement : ∀ g ∈ seeds, 180958 ≤ (agreementSet x received selected g).card
  pencil : ∀ p₀ p₁ : Polynomial K, p₀.natDegree ≤ 131071 → p₁.natDegree ≤ 131071 →
    (RCN050.pencilSeeds seeds selected p₀ p₁).card ≤ 81187

def profileShape (idx : Fin 9) : ℕ × ℕ :=
  ![(19, 185), (15, 95), (8, 54), (6, 43), (5, 38), (4, 39),
    (4, 41), (4, 44), (2, 32)] idx

theorem profile_price (idx : Fin 9) :
    ordinaryPrice 2130706433 262144 131071 180958 81186
      (profileShape idx).1 (profileShape idx).2 ≤ 250000000000000000 := by
  fin_cases idx <;> decide +kernel

private theorem ordinary_profiles_match (i : Fin 9) :
    ((ordinaryProfiles i).2.1, (ordinaryProfiles i).2.2 + (i.val + 1) * (ordinaryProfiles i).2.1) =
      profileShape i := by
  fin_cases i <;> decide +kernel

private theorem ordinary_profile_caps (i : Fin 9) :
    (profileShape i).1 ≤ 19 ∧ (profileShape i).2 ≤ 185 ∧
      (profileShape i).1 ≤ (profileShape i).2 := by
  fin_cases i <;> decide +kernel

theorem ordinary_retained_price [IsAlgClosed Ω] [CharP E 2130706433] [CharP Ω 2130706433]
    (φ : Polynomial K →+* E) (hφ : Function.Injective φ) (ψ : E →+* Ω)
    (x : I ↪ K) (σ : K →+* K) (hfixed : ∀ i, σ (x i) = x i)
    (hpow : ∀ g : K, σ g = g ^ 2130706433) (hcard : Fintype.card I = 262144)
    (U : Received K I) (retained : Finset K) (P : K → Polynomial K)
    (selection : Selection x U retained P) (q : SymbolicRow (SeedRing K))
    (hf : q.first ≠ 0) (hs : q.second ≠ 0) (hprim : IsPrimitiveRow q)
    (hδ : 11500 ≤ primitiveExcess 131071 q) (hδ' : primitiveExcess 131071 q ≤ 31612)
    (hc₂ : 2 ≤ weightDegree totalWeights (primitiveRowLift q))
    (hc₁₀ : weightDegree totalWeights (primitiveRowLift q) ≤ 10)
    (hkeep : ∀ g ∈ retained, primitiveSelected σ 2130706433 q P g = 0 ∧
      Disjoint (agreementSet x U P g)
        (primitiveBadNodes x (conjugateWord σ (U 0)) (conjugateWord σ (U 1)) q))
    (tests : ∀ (F : Carrier K), F ≠ 0 → ∀ (idx : Fin 9),
      (∀ d ∈ F.support, d 1 ≤ (profileShape idx).1 ∧ d 1 + d 2 + d 3 ≤ (profileShape idx).2) →
      HasOrdinaryAgreementTests φ ψ F x (U 0) (U 1) P retained Finset.univ 131071
        (profileShape idx).1 (profileShape idx).2) :
    ∃ idx : Fin 9, retained.card ≤ ordinaryPrice 2130706433 262144 131071 180958 81186
      (profileShape idx).1 (profileShape idx).2 := by
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
  have agreeing_count (g : ↥retained) : 180958 ≤ (agreement g).card := by
    have havoid := Finset.disjoint_left.mp (hkeep g.1 g.2).2
    have eq : (agree g.1).filter (· ∉ bad) = agree g.1 :=
      Finset.filter_true_of_mem (fun i hi hb => havoid hi hb)
    change 180958 ≤ ((agree g.1).subtype (· ∉ bad)).card
    rw [Finset.card_subtype, eq]
    exact selection.agreement g.1 g.2
  have natDegree (g : ↥retained) : (P g.1).natDegree ≤ 131071 := selection.degree_le g.1 g.2
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
  obtain ⟨idx, _, hF⟩ := exists_ordinary_carrier_of_primitive goodX
    (fun i => U 0 i.1) (fun i => U 1 i.1) (fun i => σ (U 0 i.1)) (fun i => σ (U 1 i.1))
    good_count q hprim hf hs hδ hδ' hc₂ hc₁₀ good_node σ 2130706433 P Subtype.val agreement
    natDegree agreeing_count agrees₀ agrees₁ (fun g => (hkeep g.1 g.2).1)
  dsimp at hF
  obtain ⟨F, hF, support, zero⟩ := hF
  have hshape := ordinary_profiles_match idx
  have hy' := congrArg Prod.fst hshape
  have ht' := congrArg Prod.snd hshape
  have support' : ∀ d ∈ F.support, d 1 ≤ (profileShape idx).1 ∧
      d 1 + d 2 + d 3 ≤ (profileShape idx).2 := by
    simpa only [← hy', ← ht'] using support
  obtain ⟨hy, ht, hyt⟩ := ordinary_profile_caps idx
  have price := ordinary_carrier_seed_count φ hφ ψ F hF (profileShape idx).1 (profileShape idx).2
    hy ht hyt support' x (U 0) (U 1) P retained Finset.univ 131071 180958 81186 (by decide) (by decide)
    (by rw [Finset.card_univ, hcard]; decide)
    selection.degree_le (fun g hg => zero ⟨g, hg⟩) selection.agreement
    selection.pencil (tests F hF idx support')
  rw [Finset.card_univ, hcard] at price
  exact ⟨idx, price⟩

end

end ProximityPrize.SubmissionLower.Koala6844HighOrdinary

