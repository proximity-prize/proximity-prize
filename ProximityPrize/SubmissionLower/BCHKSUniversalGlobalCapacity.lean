import ProximityPrize.SubmissionLower.BCHKSFactorPigeon
namespace ProximityPrize.SubmissionLower
open scoped BigOperators
theorem universal_positive_pair_card_le
    {F : Type*} [Field F] [DecidableEq F] [NormalizationMonoid F]
    (Q : Polynomial (Polynomial (Polynomial F))) (hQ : Q ≠ 0) (x₀ : F) (M : ℕ)
    (hQdeg : Q.natDegree ≤ M)
    (hx₀ : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      triSpecializeX R x₀ ≠ 0)
    (hdegree : ∀ R ∈ UniqueFactorizationMonoid.normalizedFactors Q,
      (triSpecializeX R x₀).natDegree = R.natDegree) :
    (positiveNormalizedFactorPairs Q x₀).card ≤ M := by
  apply positiveNormalizedFactorPairs_card_le Q hQ x₀ M hQdeg hx₀
  intro R hR
  exact (hdegree R hR).le
theorem global_exception_union_card_le
    {σ A : Type*} [DecidableEq σ] [DecidableEq A]
    (QBad : Finset σ) (Outer : Finset A) (OuterBad : A → Finset σ)
    (qCap outerCap : ℕ)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap) :
    (QBad ∪ Outer.biUnion OuterBad).card ≤ qCap + outerCap := by
  calc
    (QBad ∪ Outer.biUnion OuterBad).card
        ≤ QBad.card + (Outer.biUnion OuterBad).card :=
          Finset.card_union_le QBad (Outer.biUnion OuterBad)
    _ ≤ QBad.card + ∑ a ∈ Outer, (OuterBad a).card := by
      exact Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ qCap + outerCap := Nat.add_le_add hQ hOuter
theorem sum_universal_pair_capacities_le
    {P : Type*} [DecidableEq P]
    (Pairs : Finset P) (resultantDegree : P → ℕ)
    (incidence errors resultCap pairCap : ℕ)
    (hresult : (∑ p ∈ Pairs, resultantDegree p) ≤ resultCap)
    (hpairs : Pairs.card ≤ pairCap) :
    (∑ p ∈ Pairs, (incidence * resultantDegree p + (errors + 1))) ≤
      incidence * resultCap + (errors + 1) * pairCap := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left incidence hresult) (by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (errors + 1) hpairs)
theorem sum_mul_div_le_mul_sum_div
    {P : Type*} [DecidableEq P]
    (Pairs : Finset P) (weight : P → ℕ) (a gap : ℕ) :
    (∑ p ∈ Pairs, (a * weight p) / gap) ≤
      (a * (∑ p ∈ Pairs, weight p)) / gap := by
  induction Pairs using Finset.induction_on with
  | empty => simp
  | @insert p Pairs hp ih =>
      rw [Finset.sum_insert hp, Finset.sum_insert hp]
      calc
        a * weight p / gap + ∑ q ∈ Pairs, a * weight q / gap
            ≤ a * weight p / gap +
                (a * (∑ q ∈ Pairs, weight q)) / gap :=
              Nat.add_le_add_left ih _
        _ ≤ (a * weight p + a * (∑ q ∈ Pairs, weight q)) / gap :=
              Nat.add_div_le_add_div _ _ _
        _ = (a * (weight p + ∑ q ∈ Pairs, weight q)) / gap := by
              rw [Nat.mul_add]
theorem sum_scaled_pair_capacities_le
    {P : Type*} [DecidableEq P]
    (Pairs : Finset P) (resultantDegree : P → ℕ)
    (nminus gap errors resultCap pairCap : ℕ)
    (hresult : (∑ p ∈ Pairs, resultantDegree p) ≤ resultCap)
    (hpairs : Pairs.card ≤ pairCap) :
    (∑ p ∈ Pairs,
        ((nminus * resultantDegree p) / gap + (errors + 1))) ≤
      (nminus * resultCap) / gap + (errors + 1) * pairCap := by
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  apply Nat.add_le_add
  · exact (sum_mul_div_le_mul_sum_div Pairs resultantDegree nminus gap).trans
      (Nat.div_le_div_right (Nat.mul_le_mul_left nminus hresult))
  · simpa [Nat.mul_comm] using Nat.mul_le_mul_left (errors + 1) hpairs
theorem sum_scaled_pair_capacities_le_of_fused
    {P : Type*} [DecidableEq P]
    (Pairs : Finset P) (resultantDegree : P → ℕ)
    (nminus gap errors resultCap pairCap fusedCap : ℕ)
    (hresult : (∑ p ∈ Pairs, resultantDegree p) ≤ resultCap)
    (hpairs : Pairs.card ≤ pairCap)
    (hfused : nminus * resultCap ≤ gap * fusedCap) :
    (∑ p ∈ Pairs,
        ((nminus * resultantDegree p) / gap + (errors + 1))) ≤
      fusedCap + (errors + 1) * pairCap := by
  refine (sum_scaled_pair_capacities_le Pairs resultantDegree nminus gap errors
    resultCap pairCap hresult hpairs).trans (Nat.add_le_add_right ?_ _)
  apply Nat.div_le_of_le_mul
  simpa [Nat.mul_comm] using hfused
theorem scaled_pair_capacity_implies_incidence
    (nminus gap resultantDegree errors fiberCard : ℕ) (hgap : 0 < gap)
    (hfiber : (nminus * resultantDegree) / gap + (errors + 1) < fiberCard) :
    nminus * resultantDegree < gap * fiberCard ∧ errors + 1 < fiberCard := by
  have hdiv : (nminus * resultantDegree) / gap < fiberCard :=
    (Nat.le_add_right _ _).trans_lt hfiber
  constructor
  · simpa [Nat.mul_comm] using Nat.lt_mul_of_div_lt hdiv hgap
  · exact (Nat.le_add_left _ _).trans_lt hfiber
theorem exists_pair_fiber_after_global_exceptions
    {σ A P : Type*} [DecidableEq σ] [DecidableEq A] [DecidableEq P]
    (S QBad : Finset σ) (Outer : Finset A) (OuterBad : A → Finset σ)
    (Pairs : Finset P) (Rel : σ → P → Prop) [DecidableRel Rel]
    (capacity : P → ℕ) (qCap outerCap : ℕ)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap)
    (hcover : ∀ s ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ p ∈ Pairs, Rel s p)
    (hlarge : qCap + outerCap + (∑ p ∈ Pairs, capacity p) < S.card) :
    ∃ p ∈ Pairs,
      capacity p <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter fun s => Rel s p).card := by
  let Bad : Finset σ := QBad ∪ Outer.biUnion OuterBad
  let Good : Finset σ := S \ Bad
  have hBad : Bad.card ≤ qCap + outerCap := by
    exact global_exception_union_card_le QBad Outer OuterBad qCap outerCap hQ hOuter
  have hBadS : (Bad ∩ S).card ≤ qCap + outerCap := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans hBad
  have hsum : (∑ p ∈ Pairs, capacity p) < Good.card := by
    simp only [Good]
    rw [Finset.card_sdiff]
    apply Nat.lt_sub_of_add_lt
    exact (Nat.add_le_add_left hBadS _).trans_lt (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlarge)
  exact exists_rel_fiber_gt_capacity Good Pairs Rel capacity
    (by simpa [Good, Bad] using hcover) hsum
theorem exists_pair_fiber_of_summed_resultant_degrees
    {σ A P : Type*} [DecidableEq σ] [DecidableEq A] [DecidableEq P]
    (S QBad : Finset σ) (Outer : Finset A) (OuterBad : A → Finset σ)
    (Pairs : Finset P) (Rel : σ → P → Prop) [DecidableRel Rel]
    (resultantDegree : P → ℕ)
    (incidence errors qCap outerCap resultCap pairCap : ℕ)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap)
    (hresult : (∑ p ∈ Pairs, resultantDegree p) ≤ resultCap)
    (hpairs : Pairs.card ≤ pairCap)
    (hcover : ∀ s ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ p ∈ Pairs, Rel s p)
    (hlarge : qCap + outerCap +
        (incidence * resultCap + (errors + 1) * pairCap) < S.card) :
    ∃ p ∈ Pairs,
      incidence * resultantDegree p + (errors + 1) <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter fun s => Rel s p).card := by
  apply exists_pair_fiber_after_global_exceptions S QBad Outer OuterBad Pairs Rel
    (fun p => incidence * resultantDegree p + (errors + 1)) qCap outerCap
    hQ hOuter hcover
  exact (Nat.add_le_add_left
    (sum_universal_pair_capacities_le Pairs resultantDegree incidence errors
      resultCap pairCap hresult hpairs) (qCap + outerCap)).trans_lt hlarge
theorem exists_pair_fiber_of_fused_resultant_ledger
    {σ A P : Type*} [DecidableEq σ] [DecidableEq A] [DecidableEq P]
    (S QBad : Finset σ) (Outer : Finset A) (OuterBad : A → Finset σ)
    (Pairs : Finset P) (Rel : σ → P → Prop) [DecidableRel Rel]
    (resultantDegree : P → ℕ)
    (nminus gap errors qCap outerCap resultCap pairCap fusedCap : ℕ)
    (hQ : QBad.card ≤ qCap)
    (hOuter : (∑ a ∈ Outer, (OuterBad a).card) ≤ outerCap)
    (hresult : (∑ p ∈ Pairs, resultantDegree p) ≤ resultCap)
    (hpairs : Pairs.card ≤ pairCap)
    (hfused : nminus * resultCap ≤ gap * fusedCap)
    (hcover : ∀ s ∈ S \ (QBad ∪ Outer.biUnion OuterBad),
      ∃ p ∈ Pairs, Rel s p)
    (hlarge : qCap + outerCap +
        (fusedCap + (errors + 1) * pairCap) < S.card) :
    ∃ p ∈ Pairs,
      (nminus * resultantDegree p) / gap + (errors + 1) <
        ((S \ (QBad ∪ Outer.biUnion OuterBad)).filter fun s => Rel s p).card := by
  apply exists_pair_fiber_after_global_exceptions S QBad Outer OuterBad Pairs Rel
    (fun p => (nminus * resultantDegree p) / gap + (errors + 1))
    qCap outerCap hQ hOuter hcover
  exact (Nat.add_le_add_left
    (sum_scaled_pair_capacities_le_of_fused Pairs resultantDegree nminus gap
      errors resultCap pairCap fusedCap hresult hpairs hfused)
    (qCap + outerCap)).trans_lt hlarge
end ProximityPrize.SubmissionLower
