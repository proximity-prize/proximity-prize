import ProximityPrize.Benchmark.TargetLower
import ProximityPrize.SubmissionLower.ContactCurveComponents

/-!
# Actual regular minimal-prime cover and finite budget aggregation

Model label: gpt-5.

The index type is constructed from the actual minimal primes of (G,T),
discarding precisely those containing the regularity polynomial H. Every
regular common point is covered, and each retained prime is non-point.
An actual finite seed set is bounded by the sum of its component subsets.

The last lemma is finite arithmetic aggregation: its per-prime incidence
bounds and summed coordinate budgets remain explicit inputs, to be supplied
by the separately checked geometric interfaces. They are not asserted here.
-/

namespace ProximityPrize.SubmissionLower.ContactRegularComponentCover

open ContactCurveComponents

noncomputable section

variable (K : Type) [Field K]

def regularComponents (G T H : MvPolynomial (Fin 3) K) :
    Finset (Ideal (MvPolynomial (Fin 3) K)) := by
  classical
  exact (componentFamily K G T).filter (fun P => H ∉ P)

abbrev RegularComponent (G T H : MvPolynomial (Fin 3) K) :=
  {P : Ideal (MvPolynomial (Fin 3) K) // P ∈ regularComponents K G T H}

variable (G T H : MvPolynomial (Fin 3) K)

theorem regularComponent_mem (C : RegularComponent K G T H) :
    C.1 ∈ componentFamily K G T := by
  classical
  exact (Finset.mem_filter.mp C.2).1

instance regularComponent_isPrime (C : RegularComponent K G T H) : C.1.IsPrime :=
  component_isPrime K G T C.1 (regularComponent_mem K G T H C)

theorem regularComponent_H_not_mem (C : RegularComponent K G T H) : H ∉ C.1 := by
  classical
  exact (Finset.mem_filter.mp C.2).2

theorem regularComponent_G_mem (C : RegularComponent K G T H) : G ∈ C.1 :=
  cutIdeal_le_component K G T C.1 (regularComponent_mem K G T H C)
    (Ideal.subset_span (Set.mem_insert G {T}))

theorem regularComponent_T_mem (C : RegularComponent K G T H) : T ∈ C.1 :=
  cutIdeal_le_component K G T C.1 (regularComponent_mem K G T H C)
    (Ideal.subset_span (Set.mem_insert_of_mem G (Set.mem_singleton T)))

theorem regularComponent_ne_point (C : RegularComponent K G T H) (v : Fin 3 → K) :
    C.1 ≠ RingHom.ker (MvPolynomial.aeval v).toRingHom :=
  component_ne_pointKernel K G T C.1 (regularComponent_mem K G T H C) v

/-- Actual regular common points are covered by the constructed regular
subfamily, including when the full component family is empty. -/
theorem exists_regular_component (v : Fin 3 → K)
    (hG : MvPolynomial.eval v G = 0) (hT : MvPolynomial.eval v T = 0)
    (hH : MvPolynomial.eval v H ≠ 0) :
    ∃ C : RegularComponent K G T H,
      C.1 ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
  classical
  obtain ⟨P, hP, hv⟩ := exists_component_of_common_point K G T v hG hT
  have hnot : H ∉ P := by
    intro h
    exact hH (hv h)
  exact ⟨⟨P, Finset.mem_filter.mpr ⟨hP, hnot⟩⟩, hv⟩

def componentSeeds {Seed : Type*} (S : Finset Seed) (v : Seed → Fin 3 → K)
    (C : RegularComponent K G T H) : Finset Seed := by
  classical
  exact S.filter (fun γ => C.1 ≤ RingHom.ker (MvPolynomial.aeval (v γ)).toRingHom)

theorem componentSeeds_subset {Seed : Type*}
    (S : Finset Seed) (v : Seed → Fin 3 → K) (C : RegularComponent K G T H) :
    componentSeeds K G T H S v C ⊆ S := by
  classical
  exact Finset.filter_subset _ _

theorem componentSeeds_on_prime {Seed : Type*}
    (S : Finset Seed) (v : Seed → Fin 3 → K) (C : RegularComponent K G T H)
    (γ : Seed) (hγ : γ ∈ componentSeeds K G T H S v C) :
    C.1 ≤ RingHom.ker (MvPolynomial.aeval (v γ)).toRingHom := by
  classical
  exact (Finset.mem_filter.mp hγ).2

/-- No disjointness of the component subsets is assumed: overlaps only
increase the sum and therefore are safe for this upper bound. -/
theorem card_le_sum_componentSeeds {Seed : Type*}
    (S : Finset Seed) (v : Seed → Fin 3 → K)
    (hG : ∀ γ ∈ S, MvPolynomial.eval (v γ) G = 0)
    (hT : ∀ γ ∈ S, MvPolynomial.eval (v γ) T = 0)
    (hH : ∀ γ ∈ S, MvPolynomial.eval (v γ) H ≠ 0) :
    S.card ≤ ∑ C : RegularComponent K G T H, (componentSeeds K G T H S v C).card := by
  classical
  letI : DecidableEq Seed := Classical.decEq Seed
  have hcover : S ⊆ Finset.univ.biUnion (componentSeeds K G T H S v) := by
    intro γ hγ
    obtain ⟨C, hC⟩ := exists_regular_component K G T H (v γ) (hG γ hγ) (hT γ hγ) (hH γ hγ)
    apply Finset.mem_biUnion.mpr
    exact ⟨C, Finset.mem_univ C, Finset.mem_filter.mpr ⟨hγ, hC⟩⟩
  exact (Finset.card_le_card hcover).trans (Finset.card_biUnion_le)

/-- Sum independently proved per-prime bounds against a single summed
coordinate budget. This is the explicit finite arithmetic step, not a
replacement for deriving either of its geometric premises. -/
theorem aggregate_component_incidence {Seed : Type*}
    (S : Finset Seed) (v : Seed → Fin 3 → K)
    (hG : ∀ γ ∈ S, MvPolynomial.eval (v γ) G = 0)
    (hT : ∀ γ ∈ S, MvPolynomial.eval (v γ) T = 0)
    (hH : ∀ γ ∈ S, MvPolynomial.eval (v γ) H ≠ 0)
    (gap nodes pencil : ℕ) (cap budget : Fin 3 → ℕ)
    (degree : RegularComponent K G T H → Fin 3 → ℕ)
    (hcomponent : ∀ C,
      (componentSeeds K G T H S v C).card * gap ≤
        nodes * (∑ i, cap i * degree C i) + pencil * gap * degree C 2)
    (hbudget : ∀ i, (∑ C, degree C i) ≤ budget i) :
    S.card * gap ≤ nodes * (∑ i, cap i * budget i) + pencil * gap * budget 2 := by
  classical
  have hfubini : (∑ C : RegularComponent K G T H, ∑ i : Fin 3, cap i * degree C i) =
      ∑ i : Fin 3, cap i * (∑ C : RegularComponent K G T H, degree C i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  calc
    S.card * gap ≤ (∑ C : RegularComponent K G T H,
        (componentSeeds K G T H S v C).card) * gap :=
      Nat.mul_le_mul_right gap (card_le_sum_componentSeeds K G T H S v hG hT hH)
    _ = ∑ C : RegularComponent K G T H,
        (componentSeeds K G T H S v C).card * gap := by rw [Finset.sum_mul]
    _ ≤ ∑ C : RegularComponent K G T H,
        (nodes * (∑ i, cap i * degree C i) + pencil * gap * degree C 2) :=
      Finset.sum_le_sum (fun C _ => hcomponent C)
    _ = nodes * (∑ i : Fin 3, cap i * (∑ C : RegularComponent K G T H, degree C i)) +
        pencil * gap * (∑ C : RegularComponent K G T H, degree C 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hfubini]
    _ ≤ nodes * (∑ i, cap i * budget i) + pencil * gap * budget 2 :=
      Nat.add_le_add
        (Nat.mul_le_mul_left nodes (Finset.sum_le_sum
          (fun i _ => Nat.mul_le_mul_left (cap i) (hbudget i))))
        (Nat.mul_le_mul_left (pencil * gap) (hbudget 2))

end

end ProximityPrize.SubmissionLower.ContactRegularComponentCover

#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.regularComponent_isPrime
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.regularComponent_H_not_mem
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.regularComponent_G_mem
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.regularComponent_T_mem
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.regularComponent_ne_point
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.exists_regular_component
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.card_le_sum_componentSeeds
#print axioms ProximityPrize.SubmissionLower.ContactRegularComponentCover.aggregate_component_incidence
