import ProximityPrize.SubmissionLower.Pack_K1Defs
import ProximityPrize.SubmissionLower.Fast023
import ProximityPrize.SubmissionLower.Fast029
import ProximityPrize.SubmissionLower.Pack_K1_14_3Split
set_option Elab.async false

section PackSource_K1_14_3_2Support
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

namespace K1_14_3_2

noncomputable section

open K1_14 K1_14_3

private theorem minimalPairHeight {P Q : Jet} (h : ProperPair P Q)
    {q : Ideal Jet} (hq : q ∈ (Ideal.span {P, Q}).minimalPrimes) : q.height = 2 := by
  classical
  have : q.IsPrime := hq.1.1
  have hP : P ∈ q := hq.1.2 (Ideal.subset_span (by simp))
  have hQ : Q ∈ q := hq.1.2 (Ideal.subset_span (by simp))
  have hq₀ : q ≠ ⊥ := fun he => h.left_ne (by simpa [he] using hP)
  obtain ⟨D, hD, hp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹q.IsPrime› hq₀
  let J := Ideal.span ({D} : Set Jet)
  have : J.IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp
  have hJ₀ : J ≠ ⊥ := fun he => hp.ne_zero (Ideal.span_singleton_eq_bot.mp he)
  have hJq : J < q := by
    refine lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem q).mpr hD) ?_
    intro he
    exact h.no_common D hp.irreducible
      (Ideal.mem_span_singleton.mp (he ▸ hP : P ∈ J))
      (Ideal.mem_span_singleton.mp (he ▸ hQ : Q ∈ J))
  have hJ₁ : 1 ≤ J.height :=
    Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hJ₀)
  have htop : q.height ≤ 2 := by
    let s : Finset Jet := {P, Q}
    have hs : q ∈ (Ideal.span (s : Set Jet)).minimalPrimes := by
      simpa [s] using hq
    exact (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hs).trans
      (by exact_mod_cast (Finset.card_insert_le P {Q}).trans (by simp))
  exact le_antisymm htop <|
    calc
      2 = 1 + 1 := by decide
      _ ≤ J.height + 1 := add_le_add_left hJ₁ 1
      _ ≤ q.height := Ideal.height_add_one_le_of_lt_of_isPrime hJq

/-- Every actual point of a proper pair belongs to a height-two minimal prime. -/
theorem properPairCover {P Q : Jet} (h : ProperPair P Q) :
    ∃ qs : Finset Surface, ComponentsOn P Q qs ∧
      ∀ z S, jetAt P z S = 0 → jetAt Q z S = 0 → ∃ q ∈ qs, AtSurface q z S := by
  classical
  let J : Ideal Jet := Ideal.span {P, Q}
  let s := (J.finite_minimalPrimes_of_isNoetherianRing Jet).toFinset
  have hs (I : Ideal Jet) : I ∈ s ↔ I ∈ J.minimalPrimes := Set.Finite.mem_toFinset _
  let mk (i : {I // I ∈ s}) : Surface := ⟨i.1, ((hs i.1).mp i.2).1.1⟩
  refine ⟨s.attach.image mk, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have hi : i.1 ∈ J.minimalPrimes := (hs i.1).mp i.2
    exact ⟨minimalPairHeight h hi, hi.1.2 (Ideal.subset_span (by simp)),
      hi.1.2 (Ideal.subset_span (by simp))⟩
  · intro z S hP hQ
    let e := markEval z S
    have : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    have hJ : J ≤ RingHom.ker e := by
      apply Ideal.span_le.mpr
      intro r hr
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
      rcases hr with rfl | rfl
      · exact hP
      · exact hQ
    obtain ⟨I, hI, hIe⟩ := Ideal.exists_minimalPrimes_le hJ
    let i : {I // I ∈ s} := ⟨I, (hs I).mpr hI⟩
    exact ⟨mk i, Finset.mem_image.mpr ⟨i, Finset.mem_attach _ _, rfl⟩, hIe⟩

end
end K1_14_3_2
end PackSource_K1_14_3_2Support

section PackSource_K1_14_3_4Defs
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

namespace K1_14_3_4

noncomputable section

open K1 K1_14 K1_14_3 K1_14_3_2 Polynomial
open scoped BigOperators

/-- The written ordinary compatibility equation, in the original four coordinates. -/
def graphCutter (g : ClearedEquation) : Jet :=
  C (liftEquation (clearedDx g)) +
    (Polynomial.X (R := Equation)) * C (liftEquation g.derivative)

/-- At threshold r, keep one copy of each heavy ordinary irreducible.
The second alternative measures the order after dividing out the full gcd. -/
structure ThresholdPair (i : Fin 4) (P Q : Jet) (r : ℕ) where
  left : Jet
  right : Jet
  proper : ProperPair left right
  left_caps : RowCaps left (cheapShape i)
  right_caps : RowCaps right (layeredShape i)
  heavy : Finset Equation
  factors : ∀ f ∈ heavy, Irreducible f ∧ 0 < f.natDegree ∧ f.natDegree < p ∧
    C f ∣ P ∧ C f ∣ Q
  seed_budget : (∑ f ∈ heavy, (ordinarySeedDegree f : ℚ)) ≤ (cheapShape i).U / (r : ℚ)
  y_budget : (∑ f ∈ heavy, (f.natDegree : ℚ)) ≤ (cheapShape i).B / (r : ℚ)
  residual_order : ∀ q : Surface, Parent q →
    OrderAt q P (reserve i + 1) → OrderAt q Q (reserve i + 1) →
    (∀ f ∈ heavy, C f ∉ q.asIdeal) →
    OrderAt q left (reserve i + 2 - r) ∧ OrderAt q right (reserve i + 2 - r)

private def localLength {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime]
    (J : Ideal R) : ℕ∞ :=
  let A := Localization.AtPrime q
  Module.length A (A ⧸ J.map (algebraMap R A))

/-- Intersection multiplicity in the two-dimensional ambient local ring. -/
def intersectionLength (q : Surface) (P Q : Jet) : ℕ∞ :=
  localLength q.asIdeal (Ideal.span {P, Q})

private theorem localLength_pos {R : Type*} [CommRing R] (q J : Ideal R) [q.IsPrime]
    (hJ : J ≤ q) : 0 < localLength q J := by
  let A := Localization.AtPrime q
  have hn : J.map (algebraMap R A) ≠ ⊤ := by
    apply ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal q A]
    exact Ideal.map_mono hJ
  change 0 < Module.length A (A ⧸ J.map (algebraMap R A))
  exact Module.length_pos_iff.mpr (Ideal.Quotient.nontrivial_iff.mpr hn)

theorem intersectionLength_one {q : Surface} {P Q : Jet}
    (hP : P ∈ q.asIdeal) (hQ : Q ∈ q.asIdeal) : 1 ≤ intersectionLength q P Q := by
  apply Order.one_le_iff_pos.mpr
  apply localLength_pos
  apply Ideal.span_le.mpr
  intro t ht
  change t ∈ q.asIdeal
  rcases Set.mem_insert_iff.mp ht with rfl | ht
  · exact hP
  · rw [Set.mem_singleton_iff.mp ht]
    exact hQ

/-- The affine scheme cut by the residual equations and the two section equations. -/
def pairSectionDegree (P Q : Jet) (s : Slice) : ℕ :=
  let J := Ideal.span ({sectionMap P, sectionMap Q} : Set SectionJet) ⊔
    Ideal.span (sectionEquations s)
  Module.finrank SectionField (SectionJet ⧸ J)

/-- Raw proper-pair budgets for the three slices in the contract. -/
def residualSeed (f g : Shape) : ℚ :=
  (f.B : ℚ) * g.J + (g.B : ℚ) * f.J - (f.J : ℚ) * g.J

def residualOrdinate (f g : Shape) : ℚ :=
  (f.U : ℚ) * g.J + (g.U : ℚ) * f.J

def residualMixed (f g : Shape) : ℚ :=
  (f.U : ℚ) * g.B + (g.U : ℚ) * f.B

end
end K1_14_3_4
end PackSource_K1_14_3_4Defs
